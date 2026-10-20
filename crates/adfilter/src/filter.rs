//! The filter: what to do with an IP packet.
//!
//! [`classify`] takes a whole IPv4 or IPv6 packet:
//! - a UDP datagram to port 53 holding a DNS query for a blocked name gets
//!   [`Verdict::Reply`]: the NXDOMAIN answer, from the server the query was
//!   sent to, back to the client (or [`Verdict::Drop`] if it does not fit);
//! - a TCP segment to port 443 whose data is a ClientHello for a blocked
//!   server name gets [`Verdict::Drop`];
//! - anything else gets [`Verdict::Pass`].
//!
//! A ClientHello may span several TCP segments; [`classify_stream`] checks
//! the start of a TCP stream once reassembled.

use crate::blocklist::Blocklist;
use crate::dns::{self, Query};
use crate::tls::{self, ClientHello};
use net::tcp::{Ipv4Tcp, Ipv6Tcp};
use net::udp::{self, Ipv4Udp, Ipv6Udp};
use untrusted::Untrusted;

/// Room for the longest NXDOMAIN answer: the header and a question with a
/// name of 255 bytes on the wire.
pub const MAX_ANSWER_LEN: usize = 512;

/// What to do with a packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Let it through.
    Pass,
    /// Drop it.
    Drop,
    /// Drop it, and send the packet `out[..n]` back instead.
    Reply(usize),
}

/// Whether the DNS message `msg` is a query for a blocked name and, if so,
/// the length of its NXDOMAIN answer written to `answer` (`None` if it does
/// not fit).
fn dns_answer(
    msg: Untrusted<&[u8]>,
    list: &Blocklist,
    answer: &mut [u8; MAX_ANSWER_LEN],
) -> Option<Option<usize>> {
    let q = match msg.validate::<Query>() {
        Ok(q) => q,
        Err(_) => return None,
    };
    if !list.blocked(q.query.name.as_bytes()) {
        return None;
    }
    Some(dns::nxdomain(q.msg, &q.query, answer))
}

/// The verdict on the UDP datagram `u` over IPv4.
fn udp_ipv4(u: Ipv4Udp, list: &Blocklist, out: &mut [u8]) -> Verdict {
    if u.header.dst_port.0 != dns::PORT {
        return Verdict::Pass;
    }
    let client = u.ip.header.src;
    let server = u.ip.header.dst;
    let client_port = u.header.src_port.0;
    let mut answer = [0u8; MAX_ANSWER_LEN];
    match dns_answer(u.payload, list, &mut answer) {
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
fn udp_ipv6(u: Ipv6Udp, list: &Blocklist, out: &mut [u8]) -> Verdict {
    if u.header.dst_port.0 != dns::PORT {
        return Verdict::Pass;
    }
    let client = u.ip.header.src;
    let server = u.ip.header.dst;
    let client_port = u.header.src_port.0;
    let mut answer = [0u8; MAX_ANSWER_LEN];
    match dns_answer(u.payload, list, &mut answer) {
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
fn hello_blocked(stream: Untrusted<&[u8]>, list: &Blocklist) -> bool {
    match stream.validate::<ClientHello>() {
        Ok(c) => match c.server_name {
            Some(n) => list.blocked(n.as_bytes()),
            None => false,
        },
        Err(_) => false,
    }
}

/// The verdict on a TCP segment to `dst_port` carrying `data`.
fn tcp_verdict(dst_port: u16, data: Untrusted<&[u8]>, list: &Blocklist) -> Verdict {
    if dst_port != tls::PORT {
        return Verdict::Pass;
    }
    if hello_blocked(data, list) {
        Verdict::Drop
    } else {
        Verdict::Pass
    }
}

/// What to do with the IP packet `packet`; a reply is written to the start
/// of `out`.
pub fn classify(packet: &[u8], list: &Blocklist, out: &mut [u8]) -> Verdict {
    if let Ok(u) = Untrusted::new(packet).validate::<Ipv4Udp>() {
        return udp_ipv4(u, list, out);
    }
    if let Ok(u) = Untrusted::new(packet).validate::<Ipv6Udp>() {
        return udp_ipv6(u, list, out);
    }
    if let Ok(t) = Untrusted::new(packet).validate::<Ipv4Tcp>() {
        return tcp_verdict(t.header.dst_port.0, t.payload, list);
    }
    if let Ok(t) = Untrusted::new(packet).validate::<Ipv6Tcp>() {
        return tcp_verdict(t.header.dst_port.0, t.payload, list);
    }
    Verdict::Pass
}

/// Whether the start of a TCP stream to port 443, reassembled, is a
/// ClientHello for a blocked server name: then the connection should be
/// dropped.
pub fn classify_stream(stream: &[u8], list: &Blocklist) -> bool {
    hello_blocked(Untrusted::new(stream), list)
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
        let mut m = std::vec![0x12, 0x34, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0];
        for label in name.split('.') {
            m.push(label.len() as u8);
            m.extend_from_slice(label.as_bytes());
        }
        m.extend_from_slice(&[0, 0, 1, 0, 1]);
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
        let v = classify(&udp4(53, &q), &list, &mut out);
        let Verdict::Reply(n) = v else { panic!("{v:?}") };
        // From the server to the client, with the NXDOMAIN answer.
        let u = Untrusted::new(&out[..n]).validate::<Ipv4Udp>().ok().unwrap();
        assert_eq!(u.ip.header.src, Ipv4Addr(u32::from_be_bytes(SERVER)));
        assert_eq!(u.ip.header.dst, Ipv4Addr(u32::from_be_bytes(CLIENT)));
        assert_eq!((u.header.src_port.0, u.header.dst_port.0), (53, 5353));
        assert_eq!(&out[28..32], &[0x12, 0x34, 0x81, 0x83]);
        assert_eq!(&out[40..n], &q[12..]);
        // Over IPv6 too.
        let v = classify(&udp6(53, &q), &list, &mut out);
        assert!(matches!(v, Verdict::Reply(m) if m == 48 + q.len()));
        // Too little room for the answer.
        assert_eq!(classify(&udp4(53, &q), &list, &mut out[..40]), Verdict::Drop);
    }

    #[test]
    fn passes_other_queries() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        assert_eq!(classify(&udp4(53, &query("example.com")), &list, &mut out), Verdict::Pass);
        assert_eq!(classify(&udp4(53, &query("badads.example")), &list, &mut out), Verdict::Pass);
        assert_eq!(classify(&udp4(5353, &query("ads.example")), &list, &mut out), Verdict::Pass);
        assert!(Untrusted::new(&query("ads.example")[..]).validate::<DnsQuery>().is_ok());
    }

    #[test]
    fn drops_blocked_client_hellos() {
        let (mut data, mut ends) = (Vec::new(), Vec::new());
        let list = list(&mut data, &mut ends);
        let mut out = [0u8; 1500];
        assert_eq!(classify(&tcp4(443, &hello(b"x.tracker.io")), &list, &mut out), Verdict::Drop);
        assert_eq!(classify(&tcp4(443, &hello(b"example.org")), &list, &mut out), Verdict::Pass);
        assert_eq!(classify(&tcp4(80, &hello(b"tracker.io")), &list, &mut out), Verdict::Pass);
        assert!(classify_stream(&hello(b"TRACKER.io"), &list));
        assert!(!classify_stream(&hello(b"tracker.io.example"), &list));
        // Not a packet at all.
        assert_eq!(classify(&[0x45, 0, 0], &list, &mut out), Verdict::Pass);
    }
}
