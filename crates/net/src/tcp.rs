//! TCP segments (RFC 9293).
//!
//! ```text
//! | src port (2) | dst port (2) | sequence (4) | acknowledgment (4) |
//! | data offset/reserved (1) | flags (1) | window (2) | checksum (2) | urgent (2) |
//! | options | payload |
//! ```
//!
//! As with UDP, the checksum covers a pseudo-header made of fields of the IP
//! header, so a segment is validated together with the packet that carries
//! it: [`Ipv4Tcp`] takes a whole IPv4 packet, [`Ipv6Tcp`] a whole IPv6
//! packet. Only single segments are decoded: there is no reassembly of
//! streams. Options are handed back without being interpreted.

use crate::inet;
use crate::ipv4::{self, Ipv4Packet};
use crate::ipv6::{self, Ipv6Packet};
use crate::udp::{ipv4_header, ipv6_header, put_bytes};
use untrusted::{encode_into, BigEndian, Decode, Encode, Untrusted, Validate, ValidationError};

/// The protocol number (IPv4) and next header (IPv6) of TCP.
pub const PROTO_TCP: u8 = 6;
/// Length of a header without options.
pub const MIN_HEADER_LEN: usize = 20;

/// The fixed part of the TCP header.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct TcpHeader {
    pub src_port: BigEndian<u16>,
    pub dst_port: BigEndian<u16>,
    pub seq: BigEndian<u32>,
    pub ack: BigEndian<u32>,
    /// The data offset (the header length in 32-bit words) in the top four
    /// bits; the rest is reserved.
    pub offset: BigEndian<u8>,
    /// CWR, ECE, URG, ACK, PSH, RST, SYN, FIN, from the top bit down.
    pub flags: BigEndian<u8>,
    pub window: BigEndian<u16>,
    pub checksum: BigEndian<u16>,
    pub urgent: BigEndian<u16>,
}

/// A segment's header, options and payload, located in `segment` (the IP
/// payload), if it has a well-formed header: at least 20 bytes, and a data
/// offset `off` with `5 <= off` and `4 * off <= segment.len()`. Returns the
/// header and the header length.
fn header(segment: &[u8]) -> Result<(TcpHeader, usize), ValidationError> {
    if segment.len() < MIN_HEADER_LEN {
        return Err(ValidationError::EndOfInput);
    }
    let header = Untrusted::new(&segment[..MIN_HEADER_LEN]).read_all::<TcpHeader>()?;
    let off = (header.offset.0 / 16) as usize;
    if off < 5 {
        return Err(ValidationError::OutOfRange);
    }
    if 4 * off > segment.len() {
        return Err(ValidationError::EndOfInput);
    }
    Ok((header, 4 * off))
}

/// A TCP segment carried by an IPv4 packet.
///
/// Accepts exactly the IPv4 packets ([`Ipv4Packet`]) with protocol 6 that are
/// not fragments, whose payload (the segment) is at least 20 bytes long, has
/// a data offset `off` with `5 <= off` and `4 * off <=` its length, and a
/// valid Internet checksum over the pseudo-header (source and destination
/// address, a zero byte, the protocol, the segment length) followed by the
/// segment.
pub struct Ipv4Tcp<'a> {
    pub ip: Ipv4Packet<'a>,
    pub header: TcpHeader,
    pub options: Untrusted<&'a [u8]>,
    pub payload: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Ipv4Tcp<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv4Packet>()?;
        if ip.header.protocol.0 != PROTO_TCP {
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
        let segment = &input[header_len..total_len];
        let (header, hl) = header(segment)?;
        // The pseudo-header: the addresses, a zero byte and the protocol,
        // then the segment length (at most 65535: the IPv4 total length is
        // 16 bits).
        let len = segment.len();
        let acc = inet::sum(0, &input[12..20]);
        let acc = inet::sum(acc, &[0, PROTO_TCP]);
        let acc = inet::sum(acc, &[(len / 256) as u8, (len % 256) as u8]);
        if inet::sum(acc, segment) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        Ok(Ipv4Tcp {
            ip,
            header,
            options: Untrusted::new(&segment[MIN_HEADER_LEN..hl]),
            payload: Untrusted::new(&segment[hl..]),
        })
    }
}

/// A TCP segment carried by an IPv6 packet.
///
/// Accepts exactly the IPv6 packets ([`Ipv6Packet`]) whose next header is 6
/// (so with no extension headers), whose payload (the segment) is at least 20
/// bytes long, has a data offset `off` with `5 <= off` and `4 * off <=` its
/// length, and a valid Internet checksum over the pseudo-header (source and
/// destination address, the segment length as 32 bits, three zero bytes, the
/// next header 6) followed by the segment.
pub struct Ipv6Tcp<'a> {
    pub ip: Ipv6Packet<'a>,
    pub header: TcpHeader,
    pub options: Untrusted<&'a [u8]>,
    pub payload: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Ipv6Tcp<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv6Packet>()?;
        if ip.header.next_header.0 != PROTO_TCP {
            return Err(ValidationError::OutOfRange);
        }
        // `ip.payload`, located again: `Ipv6Packet` accepted the input, so it
        // has a full header and the payload is within it.
        let end = ipv6::payload_end(input);
        let segment = &input[ipv6::HEADER_LEN..end];
        let (header, hl) = header(segment)?;
        // The pseudo-header: the addresses, the segment length as 32 bits (at
        // most 65535: the IPv6 payload length is 16 bits), three zero bytes
        // and the next header.
        let len = segment.len();
        let acc = inet::sum(0, &input[8..40]);
        let acc = inet::sum(acc, &[0, 0]);
        let acc = inet::sum(acc, &[(len / 256) as u8, (len % 256) as u8]);
        let acc = inet::sum(acc, &[0, 0, 0, PROTO_TCP]);
        if inet::sum(acc, segment) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        Ok(Ipv6Tcp {
            ip,
            header,
            options: Untrusted::new(&segment[MIN_HEADER_LEN..hl]),
            payload: Untrusted::new(&segment[hl..]),
        })
    }
}

/// The ACK flag.
pub const FLAG_ACK: u8 = 0x10;
/// The RST flag.
pub const FLAG_RST: u8 = 0x04;
/// Length of an IPv4 packet carrying a bare segment.
pub const BARE_IPV4_LEN: usize = 40;
/// Length of an IPv6 packet carrying a bare segment.
pub const BARE_IPV6_LEN: usize = 60;

/// A TCP header without options: data offset 5, window 0, urgent pointer 0.
fn tcp_header(src_port: u16, dst_port: u16, seq: u32, ack: u32, flags: u8, checksum: u16) -> [u8; 20] {
    let h = TcpHeader {
        src_port: BigEndian(src_port),
        dst_port: BigEndian(dst_port),
        seq: BigEndian(seq),
        ack: BigEndian(ack),
        offset: BigEndian(0x50),
        flags: BigEndian(flags),
        window: BigEndian(0),
        checksum: BigEndian(checksum),
        urgent: BigEndian(0),
    };
    let mut b = [0u8; 20];
    let _ = encode_into(&h, &mut b);
    b
}

/// Writes to the start of `out` an IPv4 packet (no options, not fragmented,
/// don't-fragment set) carrying a bare TCP segment, with no options or data,
/// from `src:src_port` to `dst:dst_port` with `seq`, `ack` and `flags`, both
/// checksums computed: a reset, for instance. Returns its length
/// ([`BARE_IPV4_LEN`]), or `None` if `out` is too short.
///
/// `proofs/Net/TcpEncode.lean` proves that [`Ipv4Tcp`] accepts the result
/// and decodes it back to these addresses, ports, numbers and flags.
#[allow(clippy::too_many_arguments)]
pub fn encode_ipv4(
    src: ipv4::Ipv4Addr,
    dst: ipv4::Ipv4Addr,
    src_port: u16,
    dst_port: u16,
    seq: u32,
    ack: u32,
    flags: u8,
    out: &mut [u8],
) -> Option<usize> {
    if out.len() < BARE_IPV4_LEN {
        return None;
    }
    // Each checksum is computed with its field 0, as `Ipv4Tcp` checks it.
    let zero = ipv4_header(src.0, dst.0, 40, PROTO_TCP, 0);
    let header = ipv4_header(src.0, dst.0, 40, PROTO_TCP, 0xFFFF - inet::sum(0, &zero));
    let seg0 = tcp_header(src_port, dst_port, seq, ack, flags, 0);
    // The pseudo-header: the addresses, a zero byte, the protocol and the
    // segment length (20).
    let acc = inet::sum(0, &header[12..20]);
    let acc = inet::sum(acc, &[0, PROTO_TCP, 0, 20]);
    let s = inet::sum(acc, &seg0);
    let seg = tcp_header(src_port, dst_port, seq, ack, flags, 0xFFFF - s);
    put_bytes(out, 0, &header);
    put_bytes(out, 20, &seg);
    Some(BARE_IPV4_LEN)
}

/// Writes to the start of `out` an IPv6 packet (no extension headers)
/// carrying a bare TCP segment, with no options or data, from
/// `src:src_port` to `dst:dst_port` with `seq`, `ack` and `flags`, its
/// checksum computed. Returns its length ([`BARE_IPV6_LEN`]), or `None` if
/// `out` is too short.
///
/// `proofs/Net/TcpEncode.lean` proves that [`Ipv6Tcp`] accepts the result
/// and decodes it back to these addresses, ports, numbers and flags.
#[allow(clippy::too_many_arguments)]
pub fn encode_ipv6(
    src: ipv6::Ipv6Addr,
    dst: ipv6::Ipv6Addr,
    src_port: u16,
    dst_port: u16,
    seq: u32,
    ack: u32,
    flags: u8,
    out: &mut [u8],
) -> Option<usize> {
    if out.len() < BARE_IPV6_LEN {
        return None;
    }
    let header = ipv6_header(src.0, dst.0, 20, PROTO_TCP);
    // The checksum is computed with its field 0, as `Ipv6Tcp` checks it, over
    // the pseudo-header: the addresses, the segment length (20) as 32 bits,
    // three zero bytes and the next header.
    let seg0 = tcp_header(src_port, dst_port, seq, ack, flags, 0);
    let acc = inet::sum(0, &header[8..40]);
    let acc = inet::sum(acc, &[0, 0, 0, 20, 0, 0, 0, PROTO_TCP]);
    let s = inet::sum(acc, &seg0);
    let seg = tcp_header(src_port, dst_port, seq, ack, flags, 0xFFFF - s);
    put_bytes(out, 0, &header);
    put_bytes(out, 40, &seg);
    Some(BARE_IPV6_LEN)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ipv4::tests::{packet, Count};

    /// Writes a TCP header with data offset `off` and `data_len` bytes of data
    /// after `options_len` option bytes into the IPv4 packet `buf`, with a
    /// correct checksum. Returns the packet length.
    fn segment4(buf: &mut [u8], off: u8, options_len: usize, data_len: usize) -> usize {
        let len = MIN_HEADER_LEN + options_len + data_len;
        let n = packet(buf, PROTO_TCP, 0, len, 0);
        let s = &mut buf[20..20 + len];
        s[..2].copy_from_slice(&40000u16.to_be_bytes());
        s[2..4].copy_from_slice(&443u16.to_be_bytes());
        s[4..8].copy_from_slice(&1234u32.to_be_bytes());
        s[12] = off << 4;
        s[13] = 0x18;
        s[14..16].copy_from_slice(&64240u16.to_be_bytes());
        s[16..18].fill(0);
        for (i, b) in s[20..].iter_mut().enumerate() {
            *b = i as u8;
        }
        let acc = inet::sum(0, &buf[12..20]);
        let acc = inet::sum(acc, &[0, PROTO_TCP]);
        let acc = inet::sum(acc, &(len as u16).to_be_bytes());
        let c = !inet::sum(acc, &buf[20..20 + len]);
        buf[36..38].copy_from_slice(&c.to_be_bytes());
        n
    }

    fn validate(bytes: &[u8]) -> Result<Ipv4Tcp<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Ipv4Tcp>()
    }

    #[test]
    fn accepts_segments() {
        let mut buf = [0u8; 256];
        for (off, opts, data) in [(5, 0, 0), (5, 0, 17), (8, 12, 30), (15, 40, 0)] {
            let n = segment4(&mut buf, off, opts, data);
            let t = validate(&buf[..n]).ok().unwrap();
            assert_eq!(t.header.src_port, BigEndian(40000));
            assert_eq!(t.header.dst_port, BigEndian(443));
            assert_eq!(t.header.seq, BigEndian(1234));
            assert_eq!(t.header.flags, BigEndian(0x18));
            assert_eq!(t.options.read_all::<Count>(), Ok(Count(opts)));
            assert_eq!(t.payload.read_all::<Count>(), Ok(Count(data)));
        }
    }

    #[test]
    fn rejects_malformed_segments() {
        let mut buf = [0u8; 256];
        let n = segment4(&mut buf, 5, 0, 10);
        // Corrupted data.
        let mut b = buf;
        b[n - 1] ^= 1;
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
        // A data offset below 5, or past the end.
        let n2 = segment4(&mut buf, 4, 0, 10);
        assert_eq!(validate(&buf[..n2]).err(), Some(ValidationError::OutOfRange));
        let n3 = segment4(&mut buf, 9, 0, 10);
        assert_eq!(validate(&buf[..n3]).err(), Some(ValidationError::EndOfInput));
        // Shorter than a header.
        let n4 = packet(&mut buf, PROTO_TCP, 0, 19, 0);
        assert_eq!(validate(&buf[..n4]).err(), Some(ValidationError::EndOfInput));
        // Another protocol.
        let n5 = packet(&mut buf, ipv4::PROTO_UDP, 0, 30, 0);
        assert_eq!(validate(&buf[..n5]).err(), Some(ValidationError::OutOfRange));
    }

    #[test]
    fn accepts_ipv6_segments() {
        let mut buf = [0u8; 256];
        let len = 20 + 7;
        let n = ipv6::tests::packet(&mut buf, PROTO_TCP, len, 0);
        buf[40..42].copy_from_slice(&5000u16.to_be_bytes());
        buf[42..44].copy_from_slice(&443u16.to_be_bytes());
        buf[52] = 5 << 4;
        buf[56..58].fill(0);
        let acc = inet::sum(0, &buf[8..40]);
        let acc = inet::sum(acc, &(len as u32).to_be_bytes());
        let acc = inet::sum(acc, &[0, 0, 0, PROTO_TCP]);
        let c = !inet::sum(acc, &buf[40..40 + len]);
        buf[56..58].copy_from_slice(&c.to_be_bytes());
        let t = Untrusted::new(&buf[..n]).validate::<Ipv6Tcp>().ok().unwrap();
        assert_eq!(t.header.dst_port, BigEndian(443));
        assert_eq!(t.payload.read_all::<Count>(), Ok(Count(7)));
        buf[8] ^= 1;
        assert_eq!(
            Untrusted::new(&buf[..n]).validate::<Ipv6Tcp>().err(),
            Some(ValidationError::ChecksumMismatch)
        );
    }

    #[test]
    fn encodes_bare_segments() {
        use crate::ipv4::Ipv4Addr;
        use crate::ipv6::Ipv6Addr;
        let mut out = [0u8; 64];
        let flags = FLAG_RST | FLAG_ACK;
        let n = encode_ipv4(Ipv4Addr(0x0a00_0001), Ipv4Addr(0x0a00_0002), 443, 40000, 7, 99, flags, &mut out)
            .unwrap();
        assert_eq!(n, BARE_IPV4_LEN);
        let t = validate(&out[..n]).ok().unwrap();
        assert_eq!((t.ip.header.src.0, t.ip.header.dst.0), (0x0a00_0001, 0x0a00_0002));
        let h = t.header;
        assert_eq!((h.src_port.0, h.dst_port.0, h.seq.0, h.ack.0, h.flags.0), (443, 40000, 7, 99, 0x14));
        assert_eq!(t.payload.read_all::<Count>(), Ok(Count(0)));
        let n = encode_ipv6(Ipv6Addr(1), Ipv6Addr(2), 443, 40000, u32::MAX, 0, flags, &mut out).unwrap();
        assert_eq!(n, BARE_IPV6_LEN);
        let t = Untrusted::new(&out[..n]).validate::<Ipv6Tcp>().ok().unwrap();
        assert_eq!((t.ip.header.src.0, t.ip.header.dst.0), (1, 2));
        assert_eq!((t.header.seq.0, t.header.ack.0, t.header.flags.0), (u32::MAX, 0, 0x14));
        assert!(encode_ipv4(Ipv4Addr(1), Ipv4Addr(2), 1, 2, 0, 0, 0, &mut out[..39]).is_none());
        assert!(encode_ipv6(Ipv6Addr(1), Ipv6Addr(2), 1, 2, 0, 0, 0, &mut out[..59]).is_none());
    }

    /// The exact bytes the encoders write: the wire format must not change
    /// when the encoders are rebuilt.
    #[test]
    fn golden_segments() {
        use crate::ipv4::Ipv4Addr;
        use crate::ipv6::Ipv6Addr;
        use crate::udp::encode_tests::hex;
        let mut out = [0u8; 64];
        let flags = FLAG_RST | FLAG_ACK;
        let n = encode_ipv4(Ipv4Addr(0x0a4d_0001), Ipv4Addr(0x0a4d_0002), 443, 40000, 0x1234_5678, 0x9abc_def0, flags, &mut out)
            .unwrap();
        assert_eq!(hex(&out[..n]), "4500002800004000400626340a4d00010a4d000201bb9c40123456789abcdef0501400001adf0000");
        let n = encode_ipv6(Ipv6Addr(0xfd77 << 112 | 1), Ipv6Addr(0xfd77 << 112 | 2), 443, 40000, u32::MAX, 7, flags, &mut out)
            .unwrap();
        assert_eq!(hex(&out[..n]), "6000000000140640fd770000000000000000000000000001fd77000000000000000000000000000201bb9c40ffffffff000000075014000016dc0000");
    }
}
