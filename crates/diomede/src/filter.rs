//! The filter: what to do with an IP packet.
//!
//! [`classify`] takes a whole IPv4 or IPv6 packet and a [`Policy`]:
//! - a DNS query (UDP to port 53) for a blocked name gets [`Verdict::Reply`]:
//!   the NXDOMAIN answer, from the server the query was sent to, back to the
//!   client. With [`Policy::strip_https_rr`], a query for HTTPS or SVCB
//!   records of any other name gets an answer with no records (NOERROR), so
//!   that browsers get no Encrypted ClientHello keys and show the server
//!   name in the clear;
//! - a TLS ClientHello (TCP to port 443) for a blocked server name, and with
//!   [`Policy::block_dot`] any DNS over TLS (TCP to port 853), gets
//!   [`Verdict::Reset`]: a TCP reset back to the client;
//! - with [`Policy::block_quic`] QUIC (UDP to port 443), and with
//!   [`Policy::block_dot`] DNS over QUIC (UDP to port 853), gets
//!   [`Verdict::Drop`], so that clients fall back to TCP and plain DNS;
//! - anything else gets [`Verdict::Pass`].
//!
//! A reply or reset that does not fit in `out` turns into [`Verdict::Drop`].
//! A ClientHello may span several TCP segments; [`classify_stream`] checks
//! the start of a TCP stream once reassembled.

use crate::blocklist::Blocklist;
use crate::dns::{self, Query};
use crate::tls::{self, ClientHello};
use net::tcp::{self, Ipv4Tcp, Ipv6Tcp, TcpHeader};
use net::udp::{self, Ipv4Udp, Ipv6Udp};
use untrusted::{Untrusted, Validate, ValidationError};

/// Room for the longest DNS answer: the header and a question with a name of
/// 255 bytes on the wire.
pub const MAX_ANSWER_LEN: usize = 512;
/// The port of DNS over TLS and DNS over QUIC.
pub const DOT_PORT: u16 = 853;
/// The flags of the resets: RST and ACK.
pub const RST_ACK: u8 = 0x14;

/// What the filter blocks beyond the blocklist, to close the ways around it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Policy {
    /// Drop QUIC (UDP to port 443): its ClientHello is encrypted, and
    /// browsers fall back to TCP.
    pub block_quic: bool,
    /// Reset DNS over TLS and drop DNS over QUIC (port 853): clients fall
    /// back to plain DNS.
    pub block_dot: bool,
    /// Answer every query for HTTPS or SVCB records with no records.
    pub strip_https_rr: bool,
}

/// Everything on.
pub const STRICT: Policy = Policy {
    block_quic: true,
    block_dot: true,
    strip_https_rr: true,
};

/// What to do with a packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Let it through.
    Pass,
    /// Drop it.
    Drop,
    /// Drop it, and send the DNS answer `out[..n]` back instead.
    Reply(usize),
    /// Drop it, and send the TCP reset `out[..n]` back instead.
    Reset(usize),
}

/// The bytes of a payload, as they are: the decoders below check them.
struct Data<'a>(&'a [u8]);

impl<'a> Validate<&'a [u8]> for Data<'a> {
    type Err = ValidationError;
    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        Ok(Data(input))
    }
}

/// Whether `qtype` is HTTPS or SVCB.
fn https_type(qtype: u16) -> bool {
    if qtype == dns::TYPE_HTTPS {
        return true;
    }
    qtype == dns::TYPE_SVCB
}

/// Whether the DNS message `msg` is a query to answer and, if so, the
/// length of its answer written to `answer` (`None` if it does not fit):
/// NXDOMAIN for a blocked name, else no records for HTTPS or SVCB records if
/// the policy says so.
fn dns_answer(
    msg: Untrusted<&[u8]>,
    list: &Blocklist,
    policy: &Policy,
    answer: &mut [u8; MAX_ANSWER_LEN],
) -> Option<Option<usize>> {
    let q = match msg.validate::<Query>() {
        Ok(q) => q,
        Err(_) => return None,
    };
    if list.blocked(q.query.name.as_bytes()) {
        return Some(dns::answer(q.msg, &q.query, dns::NXDOMAIN, answer));
    }
    if !policy.strip_https_rr {
        return None;
    }
    if !https_type(q.query.qtype) {
        return None;
    }
    Some(dns::answer(q.msg, &q.query, dns::NOERROR, answer))
}

/// Whether UDP to `port` (other than DNS) is dropped: QUIC, DNS over QUIC.
fn udp_dropped(policy: &Policy, port: u16) -> bool {
    if port == tls::PORT {
        return policy.block_quic;
    }
    if port == DOT_PORT {
        return policy.block_dot;
    }
    false
}

/// The verdict on the UDP datagram `u` over IPv4.
fn udp_ipv4(u: Ipv4Udp, list: &Blocklist, policy: &Policy, out: &mut [u8]) -> Verdict {
    let port = u.header.dst_port.0;
    if port != dns::PORT {
        if udp_dropped(policy, port) {
            return Verdict::Drop;
        }
        return Verdict::Pass;
    }
    let client = u.ip.header.src;
    let server = u.ip.header.dst;
    let client_port = u.header.src_port.0;
    let mut answer = [0u8; MAX_ANSWER_LEN];
    match dns_answer(u.payload, list, policy, &mut answer) {
        None => Verdict::Pass,
        Some(None) => Verdict::Drop,
        Some(Some(n)) => {
            match udp::encode_ipv4(server, client, dns::PORT, client_port, &answer[..n], out) {
                Some(m) => Verdict::Reply(m),
                None => Verdict::Drop,
            }
        }
    }
}

/// The verdict on the UDP datagram `u` over IPv6.
fn udp_ipv6(u: Ipv6Udp, list: &Blocklist, policy: &Policy, out: &mut [u8]) -> Verdict {
    let port = u.header.dst_port.0;
    if port != dns::PORT {
        if udp_dropped(policy, port) {
            return Verdict::Drop;
        }
        return Verdict::Pass;
    }
    let client = u.ip.header.src;
    let server = u.ip.header.dst;
    let client_port = u.header.src_port.0;
    let mut answer = [0u8; MAX_ANSWER_LEN];
    match dns_answer(u.payload, list, policy, &mut answer) {
        None => Verdict::Pass,
        Some(None) => Verdict::Drop,
        Some(Some(n)) => {
            match udp::encode_ipv6(server, client, dns::PORT, client_port, &answer[..n], out) {
                Some(m) => Verdict::Reply(m),
                None => Verdict::Drop,
            }
        }
    }
}

/// Whether `stream` starts with a ClientHello for a blocked server name.
fn hello_blocked(stream: &[u8], list: &Blocklist) -> bool {
    match Untrusted::new(stream).validate::<ClientHello>() {
        Ok(c) => match c.server_name {
            Some(n) => list.blocked(n.as_bytes()),
            None => false,
        },
        Err(_) => false,
    }
}

/// Whether the TCP segment to `port` carrying `data` is reset: a
/// ClientHello for a blocked name, or DNS over TLS.
fn tcp_reset(port: u16, data: &[u8], list: &Blocklist, policy: &Policy) -> bool {
    if port == tls::PORT {
        return hello_blocked(data, list);
    }
    if port == DOT_PORT {
        return policy.block_dot;
    }
    false
}

/// The sequence and acknowledgment numbers of the reset answering the
/// segment with header `h` and `len` bytes of data: the segment's
/// acknowledgment number, and its sequence number past its data (and SYN).
fn reset_numbers(h: &TcpHeader, len: usize) -> (u32, u32) {
    let syn = (h.flags.0 / 2 % 2) as u32;
    let ack = h.seq.0.wrapping_add(len as u32).wrapping_add(syn);
    (h.ack.0, ack)
}

/// The verdict on the TCP segment `t` over IPv4.
fn tcp_ipv4(t: Ipv4Tcp, list: &Blocklist, policy: &Policy, out: &mut [u8]) -> Verdict {
    let header = t.header;
    let client = t.ip.header.src;
    let server = t.ip.header.dst;
    let data = match t.payload.validate::<Data>() {
        Ok(d) => d.0,
        Err(_) => return Verdict::Pass,
    };
    if !tcp_reset(header.dst_port.0, data, list, policy) {
        return Verdict::Pass;
    }
    let (seq, ack) = reset_numbers(&header, data.len());
    let (dst_port, src_port) = (header.dst_port.0, header.src_port.0);
    match tcp::encode_ipv4(server, client, dst_port, src_port, seq, ack, RST_ACK, out) {
        Some(n) => Verdict::Reset(n),
        None => Verdict::Drop,
    }
}

/// The verdict on the TCP segment `t` over IPv6.
fn tcp_ipv6(t: Ipv6Tcp, list: &Blocklist, policy: &Policy, out: &mut [u8]) -> Verdict {
    let header = t.header;
    let client = t.ip.header.src;
    let server = t.ip.header.dst;
    let data = match t.payload.validate::<Data>() {
        Ok(d) => d.0,
        Err(_) => return Verdict::Pass,
    };
    if !tcp_reset(header.dst_port.0, data, list, policy) {
        return Verdict::Pass;
    }
    let (seq, ack) = reset_numbers(&header, data.len());
    let (dst_port, src_port) = (header.dst_port.0, header.src_port.0);
    match tcp::encode_ipv6(server, client, dst_port, src_port, seq, ack, RST_ACK, out) {
        Some(n) => Verdict::Reset(n),
        None => Verdict::Drop,
    }
}

/// What to do with the IP packet `packet` under `policy`; a reply or reset
/// is written to the start of `out`.
pub fn classify(packet: &[u8], list: &Blocklist, policy: &Policy, out: &mut [u8]) -> Verdict {
    if let Ok(u) = Untrusted::new(packet).validate::<Ipv4Udp>() {
        return udp_ipv4(u, list, policy, out);
    }
    if let Ok(u) = Untrusted::new(packet).validate::<Ipv6Udp>() {
        return udp_ipv6(u, list, policy, out);
    }
    if let Ok(t) = Untrusted::new(packet).validate::<Ipv4Tcp>() {
        return tcp_ipv4(t, list, policy, out);
    }
    if let Ok(t) = Untrusted::new(packet).validate::<Ipv6Tcp>() {
        return tcp_ipv6(t, list, policy, out);
    }
    Verdict::Pass
}

/// Whether the start of a TCP stream to port 443, reassembled, is a
/// ClientHello for a blocked server name: then the connection should be
/// reset.
pub fn classify_stream(stream: &[u8], list: &Blocklist) -> bool {
    hello_blocked(stream, list)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::dns::DnsQuery;
    use net::inet;
    use net::ipv4::Ipv4Addr;
    use net::ipv6::Ipv6Addr;
    use std::vec::Vec;

    const CLIENT: [u8; 4] = [10, 0, 0, 2];
    const SERVER: [u8; 4] = [10, 0, 0, 1];

    fn list<'a>(data: &'a mut Vec<u8>, ends: &'a mut Vec<u32>) -> Blocklist<'a> {
        for n in ["ads.example", "tracker.io"] {
            data.extend_from_slice(n.as_bytes());
            ends.push(data.len() as u32);
        }
        Blocklist::new(data, ends).unwrap()
    }

    fn query(name: &str) -> Vec<u8> {
        query_type(name, 1)
    }

    fn query_type(name: &str, qtype: u16) -> Vec<u8> {
        let mut m = std::vec![0x12, 0x34, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0];
        for label in name.split('.') {
            m.push(label.len() as u8);
            m.extend_from_slice(label.as_bytes());
        }
        m.push(0);
        m.extend_from_slice(&qtype.to_be_bytes());
        m.extend_from_slice(&[0, 1]);
        m
    }

    fn udp4(dst_port: u16, data: &[u8]) -> Vec<u8> {
        let mut out = std::vec![0; 28 + data.len()];
        let n = udp::encode_ipv4(
            Ipv4Addr(u32::from_be_bytes(CLIENT)),
            Ipv4Addr(u32::from_be_bytes(SERVER)),
            5353,
            dst_port,
            data,
            &mut out,
        )
        .unwrap();
        out.truncate(n);
        out
    }

    fn udp6(dst_port: u16, data: &[u8]) -> Vec<u8> {
        let mut out = std::vec![0; 48 + data.len()];
        let n = udp::encode_ipv6(Ipv6Addr(2), Ipv6Addr(1), 5353, dst_port, data, &mut out)
            .unwrap();
        out.truncate(n);
        out
    }

    /// An IPv4 packet with a TCP segment to `dst_port` carrying `data`.
    fn tcp4(dst_port: u16, data: &[u8]) -> Vec<u8> {
        let mut seg = std::vec![0xC0, 0x01];
        seg.extend_from_slice(&dst_port.to_be_bytes());
        seg.extend_from_slice(&[0, 0, 0, 1, 0, 0, 0, 0, 0x50, 0x18, 0xFF, 0xFF, 0, 0, 0, 0]);
        seg.extend_from_slice(data);
        let mut pseudo = CLIENT.to_vec();
        pseudo.extend_from_slice(&SERVER);
        pseudo.extend_from_slice(&[0, 6]);
        pseudo.extend_from_slice(&(seg.len() as u16).to_be_bytes());
        let c = !inet::sum(inet::sum(0, &pseudo), &seg);
        seg[16..18].copy_from_slice(&c.to_be_bytes());
        let mut p = std::vec![0x45, 0];
        p.extend_from_slice(&((20 + seg.len()) as u16).to_be_bytes());
        p.extend_from_slice(&[0, 0, 0x40, 0, 64, 6, 0, 0]);
        p.extend_from_slice(&CLIENT);
        p.extend_from_slice(&SERVER);
        let c = !inet::sum(0, &p);
        p[10..12].copy_from_slice(&c.to_be_bytes());
        p.extend_from_slice(&seg);
        p
    }

    /// A ClientHello record for `host`.
    fn hello(host: &[u8]) -> Vec<u8> {
        let mut sni = std::vec![0, 0];
        sni.extend_from_slice(&((host.len() + 5) as u16).to_be_bytes());
        sni.extend_from_slice(&((host.len() + 3) as u16).to_be_bytes());
        sni.push(0);
        sni.extend_from_slice(&(host.len() as u16).to_be_bytes());
        sni.extend_from_slice(host);
        let mut body = std::vec![3, 3];
        body.extend_from_slice(&[7; 32]);
        body.extend_from_slice(&[0, 0, 2, 0x13, 0x01, 1, 0]);
        body.extend_from_slice(&(sni.len() as u16).to_be_bytes());
        body.extend_from_slice(&sni);
        let mut r = std::vec![22, 3, 1];
        r.extend_from_slice(&((body.len() + 4) as u16).to_be_bytes());
        r.extend_from_slice(&[1, 0]);
        r.extend_from_slice(&(body.len() as u16).to_be_bytes());
        r.extend_from_slice(&body);
        r
    }

    #[test]
    fn answers_blocked_queries() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        let q = query("cdn.Ads.example");
        let v = classify(&udp4(53, &q), &list, &STRICT, &mut out);
        let Verdict::Reply(n) = v else { panic!("{v:?}") };
        // From the server to the client, with the NXDOMAIN answer.
        let u = Untrusted::new(&out[..n]).validate::<Ipv4Udp>().ok().unwrap();
        assert_eq!(u.ip.header.src, Ipv4Addr(u32::from_be_bytes(SERVER)));
        assert_eq!(u.ip.header.dst, Ipv4Addr(u32::from_be_bytes(CLIENT)));
        assert_eq!((u.header.src_port.0, u.header.dst_port.0), (53, 5353));
        assert_eq!(&out[28..32], &[0x12, 0x34, 0x81, 0x83]);
        assert_eq!(&out[40..n], &q[12..]);
        // Over IPv6 too.
        let v = classify(&udp6(53, &q), &list, &STRICT, &mut out);
        assert!(matches!(v, Verdict::Reply(m) if m == 48 + q.len()));
        // Too little room for the answer.
        assert_eq!(classify(&udp4(53, &q), &list, &STRICT, &mut out[..40]), Verdict::Drop);
    }

    #[test]
    fn passes_other_queries() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        assert_eq!(classify(&udp4(53, &query("example.com")), &list, &STRICT, &mut out), Verdict::Pass);
        assert_eq!(classify(&udp4(53, &query("badads.example")), &list, &STRICT, &mut out), Verdict::Pass);
        assert_eq!(classify(&udp4(5353, &query("ads.example")), &list, &STRICT, &mut out), Verdict::Pass);
        assert!(Untrusted::new(&query("ads.example")[..]).validate::<DnsQuery>().is_ok());
    }

    #[test]
    fn resets_blocked_client_hellos() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        let p = tcp4(443, &hello(b"x.tracker.io"));
        let v = classify(&p, &list, &STRICT, &mut out);
        let Verdict::Reset(n) = v else { panic!("{v:?}") };
        // From the server to the client: seq is the segment's ack (0), ack its
        // seq (1) past its data.
        let t = Untrusted::new(&out[..n]).validate::<Ipv4Tcp>().ok().unwrap();
        assert_eq!(t.ip.header.src, Ipv4Addr(u32::from_be_bytes(SERVER)));
        assert_eq!((t.header.src_port.0, t.header.dst_port.0), (443, 0xC001));
        let data_len = (p.len() - 40) as u32;
        assert_eq!((t.header.seq.0, t.header.ack.0, t.header.flags.0), (0, 1 + data_len, RST_ACK));
        assert_eq!(classify(&tcp4(443, &hello(b"example.org")), &list, &STRICT, &mut out), Verdict::Pass);
        assert_eq!(classify(&tcp4(80, &hello(b"tracker.io")), &list, &STRICT, &mut out), Verdict::Pass);
        assert!(classify_stream(&hello(b"TRACKER.io"), &list));
        assert!(!classify_stream(&hello(b"tracker.io.example"), &list));
        // Not a packet at all.
        assert_eq!(classify(&[0x45, 0, 0], &list, &STRICT, &mut out), Verdict::Pass);
    }

    #[test]
    fn closes_the_ways_around() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        let off = Policy { block_quic: false, block_dot: false, strip_https_rr: false };
        // HTTPS and SVCB records of any name: none.
        for qtype in [dns::TYPE_HTTPS, dns::TYPE_SVCB] {
            let q = query_type("example.org", qtype);
            let v = classify(&udp4(53, &q), &list, &STRICT, &mut out);
            assert_eq!(v, Verdict::Reply(28 + q.len()));
            assert_eq!(&out[28..32], &[0x12, 0x34, 0x81, 0x80]);
            assert_eq!(classify(&udp4(53, &q), &list, &off, &mut out), Verdict::Pass);
        }
        // Blocked names stay NXDOMAIN, whatever the type.
        let q = query_type("ads.example", dns::TYPE_HTTPS);
        assert!(matches!(classify(&udp4(53, &q), &list, &off, &mut out), Verdict::Reply(_)));
        assert_eq!(out[31], 0x83);
        // QUIC and DNS over QUIC.
        assert_eq!(classify(&udp4(443, b"quic"), &list, &STRICT, &mut out), Verdict::Drop);
        assert_eq!(classify(&udp6(853, b"doq"), &list, &STRICT, &mut out), Verdict::Drop);
        assert_eq!(classify(&udp4(443, b"quic"), &list, &off, &mut out), Verdict::Pass);
        // DNS over TLS.
        assert!(matches!(classify(&tcp4(853, b""), &list, &STRICT, &mut out), Verdict::Reset(40)));
        assert_eq!(classify(&tcp4(853, b""), &list, &off, &mut out), Verdict::Pass);
        // No room for the reset.
        let p = tcp4(853, b"");
        assert_eq!(classify(&p, &list, &STRICT, &mut out[..39]), Verdict::Drop);
    }
}
