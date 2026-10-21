//! An ad-blocking WireGuard VPN server.
//!
//! Clients connect with any WireGuard app. The verified `wireguard` device
//! (on `wg-runtime`) decrypts their packets; before a packet goes out to the
//! internet, the verified `diomede` filter decides:
//! - a DNS query for a blocked name is answered with NXDOMAIN, and a query
//!   for HTTPS records with none (so browsers show the server name), back
//!   through the tunnel;
//! - a TLS connection to a blocked server name is reset, even when its
//!   ClientHello spans several segments;
//! - QUIC and DNS over TLS or QUIC are refused, so clients fall back to what
//!   the filter sees;
//! - everything else goes on.
//!
//! This crate holds the parts the server and `ultranet-admin` share: the
//! blocklist file format ([`blob`]) and the hook on packets ([`Filter`]).

#![cfg_attr(not(test), no_std)]

pub mod blob;

use diomede::blocklist::Blocklist;
use diomede::dns;
use diomede::filter::{filter, Policy, Verdict};
use diomede::stream::Streams;
use wg_runtime::{Hook, Inner};

/// What the filter did, since the start.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Stats {
    pub passed: u64,
    /// DNS queries for blocked names, answered NXDOMAIN.
    pub nxdomain: u64,
    /// DNS queries for HTTPS or SVCB records, answered with none.
    pub nodata: u64,
    /// TCP segments answered with a reset: blocked TLS connections and DNS
    /// over TLS.
    pub reset: u64,
    /// Packets dropped: QUIC, DNS over QUIC, segments out of order, answers
    /// that did not fit.
    pub dropped: u64,
}

impl Stats {
    /// Counts a verdict, whose reply (if any) is `reply`.
    pub fn count(&mut self, v: Verdict, reply: &[u8]) {
        match v {
            Verdict::Pass => self.passed += 1,
            Verdict::Drop => self.dropped += 1,
            Verdict::Reset(_) => self.reset += 1,
            Verdict::Reply(_) => {
                // The response code, in the DNS header after the IP and UDP
                // headers.
                let at = if reply.first().is_some_and(|b| b >> 4 == 6) { 48 } else { 28 };
                if reply.get(at + 3).is_some_and(|b| b % 16 == dns::NXDOMAIN) {
                    self.nxdomain += 1;
                } else {
                    self.nodata += 1;
                }
            }
        }
    }
}

/// The hook: every packet a client sends goes through the verified filter.
pub struct Filter<'a> {
    pub list: Blocklist<'a>,
    pub streams: &'a mut Streams,
    pub policy: Policy,
    pub stats: Stats,
}

impl<'a> Filter<'a> {
    /// The verdict on `packet` at `now`, as a hook result; a reply is
    /// written to `reply`.
    pub fn decide(&mut self, packet: &[u8], now: u64, reply: &mut [u8]) -> Hook {
        let v = filter(packet, self.streams, now, &self.list, &self.policy, reply);
        let n = match v {
            Verdict::Reply(n) | Verdict::Reset(n) => n,
            _ => 0,
        };
        self.stats.count(v, &reply[..n.min(reply.len())]);
        match v {
            Verdict::Pass => Hook::Deliver,
            Verdict::Drop => Hook::Drop,
            Verdict::Reply(n) | Verdict::Reset(n) => Hook::Reply(n),
        }
    }
}

impl Inner for Filter<'_> {
    fn delivered(&mut self, packet: &[u8], now: u64, reply: &mut [u8]) -> Hook {
        self.decide(packet, now, reply)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use diomede::filter::STRICT;
    use net::ipv4::Ipv4Addr;
    use net::udp::encode_ipv4;

    fn query(name: &str, qtype: u16) -> Vec<u8> {
        let mut m = vec![0x12, 0x34, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0];
        for label in name.split('.') {
            m.push(label.len() as u8);
            m.extend_from_slice(label.as_bytes());
        }
        m.push(0);
        m.extend_from_slice(&qtype.to_be_bytes());
        m.extend_from_slice(&[0, 1]);
        let mut p = vec![0u8; 28 + m.len()];
        let n = encode_ipv4(Ipv4Addr(0x0a4d_0002), Ipv4Addr(0x0a4d_0001), 5000, 53, &m, &mut p)
            .unwrap();
        p.truncate(n);
        p
    }

    #[test]
    fn filters_and_counts() {
        let data = b"ads.example";
        let ends = [11u32];
        let list = Blocklist::new(data, &ends).unwrap();
        let mut streams: Box<Streams> = Box::new(diomede::stream::EMPTY);
        let mut f = Filter { list, streams: &mut streams, policy: STRICT, stats: Stats::default() };
        let mut reply = vec![0u8; 2048];
        assert!(matches!(f.decide(&query("x.ads.example", 1), 1, &mut reply), Hook::Reply(_)));
        assert!(matches!(f.decide(&query("example.org", 65), 2, &mut reply), Hook::Reply(_)));
        assert_eq!(f.decide(&query("example.org", 1), 3, &mut reply), Hook::Deliver);
        assert_eq!(f.stats, Stats { passed: 1, nxdomain: 1, nodata: 1, reset: 0, dropped: 0 });
    }
}
